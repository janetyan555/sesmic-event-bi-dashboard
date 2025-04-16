"""
New Zealand seismic history events data source and business intelligence 
dashboard for impact density map of each event and property addresses in 
New Zealand with correlated history seismic events visualization application, 
to visualise the impacted area and severity of a given event, and any NZ 
property address with Its historical correlated events.

This application consists of four classes:

@Source_History_Events:
  - Fetch all historical seismic event data from GeoNet via the following API, 
    with a magnitude threshold above the given value.
      http://wfs.geonet.org.nz/geonet/ows?service=WFS&version=1.0.0
      &request=GetFeature&typeName=geonet:quake_search_v1

  - Fetch the Modified Mercalli Intensity (MMI) Scale, which grades the impact 
    of an earthquake by its significance to the community, for each event, from 
    the following API.
      http://api.geonet.org.nz/quake/

  - Process the fetched station data related to a given event, obtained from the 
    following API, to derive the affected geometry polygon with intensity above 
    the given threshold.
      http://api.geonet.org.nz/intensity/strong/processed

  - Output a CSV file with seismic events metadata, MMI scale, and affected 
    polygon, with public ID as the unique identifier in each row.
  
@NZ_Addresses:
  Plots all property addresses affected by a given seismic event within the 
  affected polygon on a Folium interactive map.
  
@Event_Contour_Map:
  A class to derive the intensity contour plot of a given event, based on the 
  event and associated density station data, using the inverse distance 
  weighting algorithm.
  
@Ui_MainWindow:
  A GUI window to visualize the seismic intensity contour plot of a chosen 
  event public ID on a Folium map, and correlated seismic events with a chosen 
  NZ address.
"""

import sys
from PyQt5 import QtCore, QtGui, QtWidgets, QtWebEngineWidgets
from PyQt5.QtWidgets import QMainWindow, QApplication, QAction, qApp, QComboBox
import pandas as pd
import geopandas as gpd
import numpy as np
import matplotlib.pyplot as plt
import os
import re
from datetime import datetime
import pytz
import requests
import json
import requests
from shapely.geometry import Polygon, MultiPoint, mapping, Point
from shapely import geometry
from pyproj import Transformer
from scipy.spatial.distance import cdist
import geojsoncontour
import folium
from shapely.ops import unary_union, polygonize
from scipy.spatial import Delaunay
import math
import mapclassify
from folium import Map, FeatureGroup, Marker, LayerControl
import branca.colormap as cm

DATA_FOLDER = '../data'
NZ_ADDRESSES_FILE = 'nz-addresses_10000_sample.csv'
# NZ_ADDRESSES_FILE = 'nz-addresses.csv'
NZ_TERRITORY_DATA = 'nz.gpkg'

class Ui_MainWindow(object):
    """
    A GUI window to visualize the seismic intensity contour plot of a chosen 
    event public ID on a Folium map, and correlated seismic events with a chosen 
    NZ address.
    """

    def __init__(self, MainWindow, event_data, nz_address_gdf):
        """
        Initialising and structuring a PYQT5 GUI window, dropdown boxes and 
        click buttons to display folium maps.  
        """
        super(Ui_MainWindow, self).__init__()
        self.MainWindow = MainWindow
        self.event_data = event_data
        self.nz_address_gdf = nz_address_gdf
        MainWindow.setObjectName("MainWindow")
        MainWindow.resize(1440, 1024)
        self.centralwidget = QtWidgets.QWidget(MainWindow)
        self.centralwidget.setObjectName("centralwidget")
        self.event_map = QtWebEngineWidgets.QWebEngineView(self.centralwidget)
        self.event_map.setGeometry(QtCore.QRect(0, 0, 720, 800))
        self.addess_map = QtWebEngineWidgets.QWebEngineView(self.centralwidget)
        self.addess_map.setGeometry(QtCore.QRect(721, 0, 720, 800))
        self.event = QtWidgets.QPushButton(self.centralwidget)
        self.event.setGeometry(QtCore.QRect(260, 801, 200, 25))
        font = QtGui.QFont()
        font.setPointSize(10)
        self.event.setFont(font)
        self.event.setObjectName("event")
        self.address = QtWidgets.QPushButton(self.centralwidget)
        self.address.setGeometry(QtCore.QRect(981, 801, 200, 25))
        self.address.setFont(font)
        self.address.setObjectName("address")

        self.comboX = QComboBox(self.centralwidget)
        self.comboX.setGeometry(QtCore.QRect(0, 830, 720, 41))
        font.setPointSize(14)
        self.comboX.setFont(font)
        self.comboX.setObjectName("event_combobox")
        self.comboX.addItems(event_data.publicid.to_list())

        self.comboY = QComboBox(self.centralwidget)
        self.comboY.setGeometry(QtCore.QRect(721, 830, 720, 41))
        self.comboY.setFont(font)
        self.comboY.setObjectName("address_combobox")
        self.comboY.addItems(self.nz_address_gdf.full_address.to_list())

        self.labelX = QtWidgets.QLabel(self.centralwidget)
        self.labelX.setGeometry(QtCore.QRect(0, 850, 720, 120))
        font.setPointSize(12)
        self.labelX.setFont(font)
        self.labelX.setObjectName('labelX')
        self.labelY = QtWidgets.QLabel(self.centralwidget)
        self.labelY.setGeometry(QtCore.QRect(721, 850, 400, 120))
        self.labelY.setFont(font)
        self.labelY.setObjectName('labelY')

        MainWindow.setCentralWidget(self.centralwidget)
        self.menubar = QtWidgets.QMenuBar(MainWindow)
        self.menubar.setGeometry(QtCore.QRect(0, 0, 800, 21))
        self.menubar.setObjectName("menubar")
        self.menubar.setNativeMenuBar(False)
        MainWindow.setMenuBar(self.menubar)
        self.statusbar = QtWidgets.QStatusBar(MainWindow)
        self.statusbar.setObjectName("statusbar")
        self.statusbar.showMessage('Ready')

        self.exit_act = QAction('&Quit')
        self.exit_act.setShortcut('Ctrl+Q')
        self.exit_act.setStatusTip('Quit the Application')
        self.exit_act.triggered.connect(qApp.quit)

        self.file_menu = self.menubar.addMenu('&File')
        self.file_menu.addAction(self.exit_act)
        MainWindow.setStatusBar(self.statusbar)

        self.event.clicked.connect(self.show_event)
        self.address.clicked.connect(self.show_address)

        self.comboX.setCurrentIndex(event_data.shape[0]-1)
        self.comboY.setCurrentIndex(0)

        self.comboX.setEditable(True)
        self.comboX.setInsertPolicy(QComboBox.NoInsert)
        self.comboX.completer().setCompletionMode(QtWidgets.QCompleter.PopupCompletion)
        self.comboX.show()

        self.comboY.setEditable(True)
        self.comboY.setInsertPolicy(QComboBox.NoInsert)
        self.comboY.completer().setCompletionMode(QtWidgets.QCompleter.PopupCompletion)
        self.comboY.show()

        self.retranslateUi()
        QtCore.QMetaObject.connectSlotsByName(MainWindow)

    def retranslateUi(self):
        """
        Define title for the GUI window and text to show on the buttons.
         """
        _translate = QtCore.QCoreApplication.translate
        self.MainWindow.setWindowTitle(_translate("MainWindow", "Earthquake Event BI Dashboard"))
        self.event.setText(_translate("MainWindow", "Show Event Density Map"))
        self.address.setText(_translate("MainWindow", "Show Address History Events"))

    def show_event(self):
        """
        Bind the event combobox to plot a seismic event density Folium map by
        passing the chosen public ID to the Event_Contour_Map class when clicked.
        """
        self.zoomX = self.comboX.currentText()
        event_app = Event_Contour_Map()
        m, affected_polygon_gdf, epicenter_gdf = event_app.event_plot(self.zoomX)

        # m = folium.Map(location=[45.5236, -122.6750], zoom_start=self.zoomX)
        self.event_map.setHtml(m.get_root().render())
        self.labelX.setText(
            f"\nOrigin time: {self.event_data[self.event_data['publicid'] == self.zoomX].origintime.values[0]}"
            + f"\nMagnitude: {epicenter_gdf.magnitude.values[0]}"
            + f"\nDepth:     {epicenter_gdf.depth.values[0]}"
            + f"\nMMi:       {epicenter_gdf.mmi.values[0]}"
            + f"\nLocation:  {epicenter_gdf.description.values[0]}"
        )

    def show_address(self):
        """
        Bind the address combobox to plot a correlated hostorical seismic events
        Folium map by passing the chosen NZ Address to the NZ_Addresses class 
        when clicked.
        """	
        self.zoomY = self.comboY.currentText()
        address_app = NZ_Addresses(self.zoomY, self.nz_address_gdf)
        m = address_app.plot_map()
        self.addess_map.setHtml(m.get_root().render())

class Event_Contour_Map(object):
    """
    A class to derive the intensity contour plot of a given event, based on the 
    event and associated density station data, using the inverse distance 
    weighting algorithm.
    """

    def __init__(self):
        """
        Initialise the class.
        """
        super(Event_Contour_Map, self).__init__()

    def read_gdf_from_wkt(self, file_name, crs="epsg:2193"):
        """
        Read a CSV file into a dataframe and convert it to a geodataframe by 
        loading geomatry information from WKT.
        """
        df = pd.read_csv(
            os.path.abspath(os.path.join(os.getcwd(), DATA_FOLDER, file_name))
        )
        gdf = gpd.GeoDataFrame(
            df,
            geometry=gpd.GeoSeries.from_wkt(df["WKT"]),
            crs=crs,
        )
        return gdf

    def convert_df_to_gdf(
        self, df, x, y, from_crs="epsg:4167", to_crs="epsg:2193"
    ):
        """
        Convert a dataframe to a geodataframe by loading geomatry information 
        from coordinates.
        """	
        gdf = gpd.GeoDataFrame(
            df, geometry=gpd.points_from_xy(df[x], df[y]), crs=from_crs
        ).to_crs(to_crs)
        return gdf

    def inverse_distance_weighting(self, x, y, z, xi, yi, power=1.25, eps=1e+3):
        """
        Inverse Distance Weighting (IDW) interpolation
        :param x: array-like, x-coordinates of known data points
        :param y: array-like, y-coordinates of known data points
        :param z: array-like, values of known data points
        :param xi: array-like, x-coordinates of unknown data points
        :param yi: array-like, y-coordinates of unknown data points
        :param power: float, power parameter (default is 2)
        :param eps: float, small value to avoid division by zero (default is 1e-6)
        :return: array-like, interpolated values at unknown data points
        """
        distances = cdist(np.column_stack((x, y)), np.column_stack((xi, yi)))
        weights = 1.0 / (distances + eps) ** power
        weights /= np.sum(weights, axis=0)
        zi = np.dot(z, weights)
        return zi

    def alpha_shape(self, points, alpha, only_outer=True):
        """
        Compute the alpha shape (concave hull) of a set of points.

        @param points: Iterable container of points.
        @param alpha: alpha value to influence the gooeyness of the border. Smaller
                    numbers don't fall inward as much as larger numbers.
                    Too large, and you lose everything!
        """
        if len(points) < 4:
            # When you have a triangle, there is no sense in computing an alpha
            # shape.
            return geometry.MultiPoint(list(points)).convex_hull

        def add_edge(edges, edge_points, coords, i, j):
            """Add a line between the i-th and j-th points, if not in the list 
                already"""
            if (i, j) in edges or (j, i) in edges:
                # Can't go twice over same directed edge right?
                assert (j, i) in edges
                if only_outer:
                    # if both neighboring triangles are in shape,
                    # it's not a boundary edge
                    edges.remove((j, i))
                return
            edges.add((i, j))
            edge_points.append(coords[[i, j]])

        coords = np.array([point for point in points])

        tri = Delaunay(coords)
        edges = set()
        edge_points = []
        # loop over triangles:
        # ia, ib, ic = indices of corner points of the triangle
        for ia, ib, ic in tri.simplices:
            pa = coords[ia]
            pb = coords[ib]
            pc = coords[ic]

            # Lengths of sides of triangle
            a = math.sqrt((pa[0] - pb[0]) ** 2 + (pa[1] - pb[1]) ** 2)
            b = math.sqrt((pb[0] - pc[0]) ** 2 + (pb[1] - pc[1]) ** 2)
            c = math.sqrt((pc[0] - pa[0]) ** 2 + (pc[1] - pa[1]) ** 2)

            # Semiperimeter of triangle
            s = (a + b + c) / 2.0

            # Area of triangle by Heron's formula
            area = math.sqrt(s * abs(s - a) * abs(s - b) * abs(s - c)) + 0.0001
            circum_r = a * b * c / (4.0 * area)

            # Here's the radius filter.
            # print circum_r
            if circum_r < alpha:
                add_edge(edges, edge_points, coords, ia, ib)
                add_edge(edges, edge_points, coords, ib, ic)
                add_edge(edges, edge_points, coords, ic, ia)

        m = geometry.MultiLineString(edge_points)
        triangles = list(polygonize(m))
        return unary_union(triangles), edge_points

    def color_map(self, colour):
        """
        Setup a colour map dictionary to display the contour lines in a 
        gradient colour setting. 
        """
        colour_map_dict = {
            1: "#ffeede",
            2: "#fedfc0",
            3: "#fdb97d",
            4: "#fd8c3b",
            5: "#de5005",
            6: "#a13403",
            7: "#973103",
            8: "#8C2E02",
            9: "#852C03",
            10: "#7F2903",
            11: "#782703",
            12: "#6B2000",
        }
        return colour_map_dict.get(colour)

    def plot_map(
        self, nz_gdf, epicenter_gdf, station_gdf, affected_polygon_gdf,
            contour_gdf, epicentre_mmi
    ):
        """
        Plot a folium map for the epic centre, associated stations, intensity 
        contour plot and affected polygon of a given seismic event and NZ 
        territories.
        """
        map = folium.Map(location=[-41.3, 174.8], zoom_start=6)
        nz_gdf.explore(m=map, color="lightgrey", name="Polygons (adm. areas)")
        epicenter_gdf.explore(m=map, name="Epicentre", marker_type="marker")
        station_gdf.explore(
            m=map,
            name="Stations",
            marker_type="marker",
            tooltip=[
                "station",
                "name",
                "location",
                "mmi",
                "distance",
                "network",
                "pga_h",
                "pga_v",
                "pgv_h",
                "pgv_v",
                "station_longitude",
                "station_latitude",
            ],  # color=station_gdf["colour"],\
            style_kwds=dict(
                style_function=lambda x: {
                    "html": f"""<span   class="fa fa-broadcast-tower"
                                        style="color:{x["properties"]["colour"]};
                                        font-size:18px"></span>"""
                },
            ),
            marker_kwds=dict(icon=folium.DivIcon()),
            height=300,
            width=300,
        )
        fg_contour = FeatureGroup(name="Intensity Contours").add_to(map)
        contour_gdf.explore(
            m=fg_contour,
            color=contour_gdf["stroke"],  # scheme='maximumbreaks',\
            # cmap='Spectral',\
            # legend=True,\
            # tiles='Stamen Terrain',\
            # style_kwds =dict(color="gray", weight=0.5),\
            # legend_kwds=dict(colorbar=True)\
        )
        # mCluster_contour = MarkerCluster(name="Intensity Contour Label").add_to(m)
        for feature in contour_gdf.iterfeatures():
            coords = Transformer.from_crs(2193, 4167, always_xy=True).transform(
                feature["geometry"]["coordinates"][0][0],
                feature["geometry"]["coordinates"][0][1],
            )  # Extract coordinates for label position
            label = feature["properties"][
                "level-value"
            ]  # Extract contour level for label text
            colour = feature["properties"]["stroke"]
            contour_label = folium.Marker(
                location=[coords[1], coords[0]],
                icon=folium.DivIcon(
                    html=f'<div style="font-size: 8pt; color : white">{label}</div>'
                    # , class_name='mapText'\
                ),
            )
            fg_contour.add_child(contour_label)

        affected_polygon_gdf.explore(
            m=map, color="olivedrab",
            name="Affected Polygon",
            style_kwds={"fill": False}
        )
        label = cm.LinearColormap(
            contour_gdf.stroke,
            vmin=contour_gdf["level-value"].min(),
            vmax=epicentre_mmi
        ).to_step(len(contour_gdf.stroke))
        label.caption = "MMi"
        map.add_child(label)

        folium.LayerControl(collapsed=False).add_to(map)
        return map

    def estimate_indensity_contour(
        self,
        station_lon_array_hat,
        station_lat_array_hat,
        station_mmi_array_hat,
        cmap="Oranges",
        levels=20,
        linewidths=1,
    ):
        """
        Derive a contour plot for a given event and estimates.
        """
        contour = plt.contour(
            station_lon_array_hat,
            station_lat_array_hat,
            station_mmi_array_hat,
            cmap=cmap,
            levels=levels,
            linewidths=linewidths,
        )
        contour_gdf = gpd.GeoDataFrame.from_features(
            json.loads(
                geojsoncontour.contour_to_geojson(
                    contour=contour, min_angle_deg=3.0, ndigits=5, stroke_width=1
                )
            )
        ).set_crs("EPSG:2193")
        plt.close()
        return contour_gdf

    def form_affected_polygon(
        self,
        station_lon_array_hat,
        station_lat_array_hat,
        station_mmi_array_z,
        mmi_threshold,
        alpha,
    ):
        """
        Define the given even's affected area polygon by given mmi threshold.
        """
        points = np.column_stack(
            (
                station_lon_array_hat.flatten()[station_mmi_array_z >= 
                    mmi_threshold],
                station_lat_array_hat.flatten()[station_mmi_array_z >= 
                    mmi_threshold],
            )
        )

        # This is the most time consuming step.
        concave_hull, edge_points = self.alpha_shape(
            points,
            alpha=alpha,
            only_outer=True
        )
        polygon_gdf = gpd.GeoDataFrame(
            index=[0],
            crs="epsg:2193",
            geometry=[concave_hull]
        )
        return polygon_gdf

    def estimate_station_z_value(
        self,
        station_lon_array,
        station_lat_array,
        station_mmi_array,
        station_hat=200,
        space_extension=0,
    ):
        """
        Assign weights to each station by using the
        inverse distance weighting algorithm.
        """
        np.random.seed(7)
        station_lon_array_hat, station_lat_array_hat = np.meshgrid(
            np.linspace(
                station_lon_array.min() - space_extension,
                station_lon_array.max() + space_extension,
                station_hat,
            ),
            np.linspace(
                station_lat_array.min() - space_extension,
                station_lat_array.max() + space_extension,
                station_hat,
            ),
        )
        station_mmi_array_z = self.inverse_distance_weighting(
            station_lon_array,
            station_lat_array,
            station_mmi_array,
            station_lon_array_hat.flatten(),
            station_lat_array_hat.flatten(),
        )
        station_mmi_array_hat = station_mmi_array_z.reshape(
            station_lon_array_hat.shape
        )
        return (
            station_lon_array_hat,
            station_lat_array_hat,
            station_mmi_array_z,
            station_mmi_array_hat,
        )

    def station_feature_array_generator(
        self, station_gdf, epic_lon, epic_lat, epicentre_weight, epicentre_mmi
    ):
        """
        Adds the epic centre coordinates and repeates by a derived weight into 
        the feature array for estimations.
        """
        station_lon_list = list(station_gdf.centroid.x)
        station_lat_list = list(station_gdf.centroid.y)
        station_lon_array = np.array(
            station_lon_list + [epic_lon] * epicentre_weight
        )
        station_lat_array = np.array(
            station_lat_list + [epic_lat] * epicentre_weight
        )
        station_mmi_array = np.array(
            station_gdf.mmi.tolist() + [epicentre_mmi] * epicentre_weight
        )
        return station_lon_array, station_lat_array, station_mmi_array

    def estimate_affected_ploygon_geodataframe(self, epicenter_gdf, station_gdf):
        """
        Produce an affected area polygon with given MMi based on the coordinates
        estimated by analysing the station data oin each event.
        """
        epicentre_mmi = epicenter_gdf.mmi.values[0]
        epic_lon = epicenter_gdf.centroid.x[0]
        epic_lat = epicenter_gdf.centroid.y[0]
        epicentre_weight = max(int(station_gdf.shape[0] / 28), 1)

        (
            station_lon_array,
            station_lat_array,
            station_mmi_array,
        ) = self.station_feature_array_generator(
            station_gdf, epic_lon, epic_lat, epicentre_weight, epicentre_mmi
        )

        (
            station_lon_array_hat,
            station_lat_array_hat,
            station_mmi_array_z,
            station_mmi_array_hat,
        ) = self.estimate_station_z_value(
            station_lon_array, station_lat_array, station_mmi_array
        )

        affected_polygon_gdf = self.form_affected_polygon(
            station_lon_array_hat,
            station_lat_array_hat,
            station_mmi_array_z,
            mmi_threshold=3.5,
            alpha=7000,
        )
        return (
            affected_polygon_gdf,
            station_lon_array_hat,
            station_lat_array_hat,
            station_mmi_array_hat,
            epicentre_mmi,
        )

    def extract_epicenter_geodataframe(self, df):
        """
        Extract seismic metadata from station data and convert it to a one-row 
        geodataframe for plotting on a folium map.
        """
        gdf_column_list = [
            "event_id",
            "description",
            "depth",
            "magnitude",
            "mag_type",
            "latitude",
            "longitude",
            "epicenter_mmi",
        ]
        temp_df = df.head(1)
        gdf = self.convert_df_to_gdf(
            temp_df[gdf_column_list].head(1),
            'longitude', 
            'latitude'
        ).rename(columns={"epicenter_mmi": "mmi"})
        gdf["name"] = "epicenter"
        return gdf

    def source_station_data_with_epicenter_mmi(self, publicid):
        """
        Call the strong API from GeoNet to source stations data with coordinates
        and MMi for a given event defined by the given public ID.
        Then call the qucke API to source the epicenter MMi.
        """
        df = pd.DataFrame(columns=[1])
        response = requests.get(
            f"http://api.geonet.org.nz/intensity/strong/processed/{publicid}"
        )
        if response.status_code == 200:
            json_data = response.json()
            raw_df = pd.DataFrame(
                [
                    {
                        **json_data["metadata"],
                        **x["properties"],
                        **{
                            "station_longitude": x["geometry"]["coordinates"][0],
                            "station_latitude": x["geometry"]["coordinates"][1],
                        },
                    }
                    for x in json_data["features"]
                ]
            )
            mmi_response = requests.get(f"http://api.geonet.org.nz/quake/{publicid}")
            mmi_json_data = mmi_response.json()
            raw_df["epicenter_mmi"] = mmi_json_data["features"][0]["properties"]["mmi"]
            df = raw_df[
                (raw_df["station_longitude"] != 0) | (raw_df["station_latitude"] != 0)
            ]
        return df


    def event_plot(self, publicid):
        """
        Integrate all processes from sourcing the station data, NZ territory 
        data, to plot all information on a folium interactive map.
        """
        station_df = self.source_station_data_with_epicenter_mmi(publicid)
        if station_df.shape[0] > 0:
            nz_gdf = gpd.read_file(
                os.path.abspath(os.path.join(os.getcwd(), "../data", NZ_TERRITORY_DATA)),
                crs="EPSG:2193",
            )
            station_gdf = self.convert_df_to_gdf(
                station_df,
                'station_longitude', 
                'station_latitude'
            )
            epicenter_gdf = self.extract_epicenter_geodataframe(station_df)
            (
                affected_polygon_gdf,
                station_lon_array_hat,
                station_lat_array_hat,
                station_mmi_array_hat,
                epicentre_mmi,
            ) = self.estimate_affected_ploygon_geodataframe(epicenter_gdf, station_gdf)
            contour_gdf = self.estimate_indensity_contour(
                station_lon_array_hat, station_lat_array_hat, station_mmi_array_hat
            )
            station_gdf["colour"] = station_gdf["mmi"].apply(self.color_map)
            map = self.plot_map(
                nz_gdf,
                epicenter_gdf,
                station_gdf,
                affected_polygon_gdf,
                contour_gdf,
                epicentre_mmi,
            )
            return map, affected_polygon_gdf, epicenter_gdf
        else:
            print("Failed to fetch data.")

class NZ_Addresses(object):
    """
    Plots all property addresses affected by a given seismic event within the 
    affected polygon on a Folium interactive map.
    """
    
    def __init__(self, address, nz_address_gdf):
        """
        Create a new NZ_Addresses object with the specified address and NZ 
        addresses data.
        """
        super(NZ_Addresses, self).__init__()
        self.address = address
        self.nz_address_gdf = nz_address_gdf
    
    def prepare_data(self):
        """
        Source address metadata from NZ addresses data, source nz territory 
        data, and filter the correlated historical seismic events by searching 
        whether the events' affected polygons cover the coordinates of the 
        selected address.
        """
        event_app = Event_Contour_Map()
        event_polygon_gdf = event_app.read_gdf_from_wkt('events_2009-03-01_2024-03-01.csv')
        selected_address = self.nz_address_gdf[self.nz_address_gdf['full_address'] == self.address]
        filtered_gdf = gpd.tools.sjoin(\
                                selected_address,\
                                event_polygon_gdf.drop('WKT', axis=1),
                                predicate="within",\
                                how='inner'\
                                )[event_polygon_gdf.columns]
        epicenter_gdf = event_app.convert_df_to_gdf(filtered_gdf.drop('geometry', axis=1), 'longitude', 'latitude')
        nz_gdf = gpd.read_file(
                    os.path.abspath(os.path.join(os.getcwd(), "../data", NZ_TERRITORY_DATA)),
                    crs="EPSG:2193",
                )
        return nz_gdf, epicenter_gdf, selected_address
    
    def plot_map(self):
        """
        Plot NZ territoty, the selected NZ address and correlated history
        seismic events' metadata and locations on a folium map.
        """
        nz_gdf, epicenter_gdf, address_gdf = self.prepare_data()
        map = folium.Map(location=[-41.3, 174.8], zoom_start=6)
        nz_gdf.explore(m=map, color="lightgrey", name="Polygons (adm. areas)")
        epicenter_gdf.explore(m=map, name="Epicentre", marker_type="marker")
        address_gdf.explore(
            m=map,
            name="Address",
            marker_type="marker",
            style_kwds=dict(
                style_function=lambda x: {
                    "html": f"""<span   class="fa fa-home"
                                            style="color:orange;
                                            font-size:18px"></span>"""
                },
            ),
            marker_kwds=dict(icon=folium.DivIcon()),
            height=300,
            width=300,
        )
    
        folium.LayerControl(collapsed=False).add_to(map)
        return map

class Source_History_Events(object):
    """
    - Fetch all historical seismic event data from GeoNet via the following API, 
        with a magnitude threshold above the given value.
        http://wfs.geonet.org.nz/geonet/ows?service=WFS&version=1.0.0
        &request=GetFeature&typeName=geonet:quake_search_v1

    - Fetch the Modified Mercalli Intensity (MMI) Scale, which grades the impact 
        of an earthquake by its significance to the community, for each event, from 
        the following API.
        http://api.geonet.org.nz/quake/

    - Process the fetched station data related to a given event, obtained from the 
        following API, to derive the affected geometry polygon with intensity above 
        the given threshold.
        http://api.geonet.org.nz/intensity/strong/processed

    - Output a CSV file with seismic events metadata, MMI scale, and affected 
        polygon, with public ID as the unique identifier in each row.
    """
    
    def __init__(self, magnitude_theshold, boundary_mmi):
        """
        Create a new Source_History_Events object with the specified magnitude 
        theshold for the historical event and boundary mmi for the affacted 
        polygon.
        """
        super(Source_History_Events, self).__init__()
        self.magnitude_theshold = magnitude_theshold
        self.boundary_mmi = boundary_mmi
    
    def setFolder(self, path):
        """
        Make a folder if not exists.
        """
        if not os.path.exists(path):
            os.makedirs(path, exist_ok=True)

    def output_geodataframe_with_polygon(self, gdf, event_app):
        """
        Produce an affected area polygon with given MMi based on the coordinates
        estimated by analysing the station data oin each event.
        """
        gdf['WKT'] = None
        for index, row in gdf.iterrows():
            epicentre_mmi = row.mmi
            epic_lon = row.geometry.centroid.x
            epic_lat = row.geometry.centroid.y
            station_df = event_app.source_station_data_with_epicenter_mmi(row.publicid)
            if station_df.shape[0] > 0:
                station_gdf = event_app.convert_df_to_gdf(station_df, 'station_longitude', 'station_latitude')
                epicentre_weight = max(int(station_gdf.shape[0] / 28), 1)
                station_lon_array, station_lat_array,\
		  station_mmi_array = event_app.station_feature_array_generator(station_gdf,
	                                        epic_lon,
	                                        epic_lat,
		                                epicentre_weight,
		                                epicentre_mmi)
                station_lon_array_hat, station_lat_array_hat,\
		    station_mmi_array_z, station_mmi_array_hat = event_app.estimate_station_z_value(
		                                              station_lon_array,
		                                              station_lat_array,
		                                              station_mmi_array
		                                              )
                affected_polygon = event_app.form_affected_polygon(
		                                          station_lon_array_hat,
	                                                  station_lat_array_hat,
		                                          station_mmi_array_z,
		                               mmi_threshold = self.boundary_mmi,
	                                                  alpha = 7000
		                                          )
                gdf.at[index, 'WKT'] = affected_polygon.loc[0, 'geometry']
        return gdf

    def get_geonet_event(
        self,
        date_list,
        magnitude_theshold,
        tz="Pacific/Auckland",
        top_latitude=-32.2871,
        bottom_latitude=-49.1817,
        left_longitude=163.5205,
        right_longitude=180.5712,
    ):
        """
        Source the historical earthquake event data by calling the
        'GeoNet Web Feature Service' API with deined date range in UTC
        and mangnitude threshold and a nested API 'quake' to retrieve the
        MMi scale and location description by indexing the publicID of each
            event.

        data_list: a date range list betwen the start date and end date
            that have been converted from local time to UTC.
        magnitude_theshold: equals and above. MMi is also applied later with
            the magnitude_theshold.
        """
        df = pd.DataFrame(columns=[1])
        response = requests.get(
            "http://wfs.geonet.org.nz/geonet/ows?service=WFS&version=1.0.0&"
            + "request=GetFeature&typeName=geonet:quake_search_v1&"
            + f"outputFormat=json&cql_filter=origintime>={date_list[0]}+AND+"
            + f"origintime<{date_list[1]}+AND+magnitude>{magnitude_theshold}+AND+"
            + f"WITHIN(origin_geom,POLYGON(({left_longitude}+{top_latitude},+"
            + f"{right_longitude}+{top_latitude},+{right_longitude}+"
            + f"{bottom_latitude},+{left_longitude}+{bottom_latitude},+"
            + f"{left_longitude}+{top_latitude})))"
        )
        if response.status_code == 200:
            json_data = response.json()
            df = pd.DataFrame(
                [
                    {
                        **x["properties"],
                        **{
                            "longitude": x["geometry"]["coordinates"][0],
                            "latitude": x["geometry"]["coordinates"][1],
                        },
                    }
                    for x in json_data["features"]
                ]
            )
            if df.shape[0] > 0:
                for row in df.itertuples(index=True, name="Pandas"):
                    mmi_response = requests.get(
                        f"http://api.geonet.org.nz/quake/{row.publicid}"
                    )
                    mmi_json_data = mmi_response.json()
                    for feature in ["mmi", "locality", "quality"]:
                        df.at[row.Index, feature] = mmi_json_data["features"][0][
                            "properties"
                        ][feature]
                df = df[df["mmi"] >= magnitude_theshold]
                if df.shape[0] > 0:
                    df["origintime"] = (
                        pd.to_datetime(df["origintime"])
                        .dt.tz_convert(tz)
                        .dt.tz_localize(None)
                    )
                    df["modificationtime"] = (
                        pd.to_datetime(df["modificationtime"])
                        .dt.tz_convert(tz)
                        .dt.tz_localize(None)
                    )
        return df

    def prepare_date_range(self, start_date, end_date):
        """
        Convert given dates from local time to UTC and return a list of
        one start and one end dates to be referenced in the
        'GeoNet Web Feature Service' API GET request.
        """
        date_list = []
        time_zone = pytz.timezone("Pacific/Auckland")
        out_format = "%Y-%m-%dT%H:%M:%S.000Z"
        for date in [start_date, end_date]:
            date_time = datetime.strptime(date, "%Y-%m-%d")
            converted_date = (
                time_zone.localize(date_time).astimezone(pytz.utc).strftime(out_format)
            )
            date_list.append(converted_date)
        return date_list

    def create_date_range_dict(self, start_date, end_date):
        """
        Create a date dictionary with start dates and end dates
        in yearly frequency within the given date range.
        """
        date_dict = {}
        date_list = pd.date_range(start_date, end_date, freq='YS')\
	                                        .strftime('%Y-%m-01').tolist()
        start_date_list = sorted(set([start_date] + date_list))
        end_date_list = sorted(set(list(start_date_list)[1:] + [end_date]))

        for start, end in zip(start_date_list, end_date_list):
            date_dict[f'{start}_{end}'] = (start, end)
        return date_dict

    def input_dates(self):
        """
        Fetch a start date and an end date from user input in a limited range 
        and format.
        """
        start_date = input(
            'Please enter a start date ranging from year 2000 in "yyyy-mm-dd" format: '
        ).strip()
        while not bool(
            re.match("^20[0-2][0-9]-((0[1-9])|(1[0-2]))-([0-2][1-9]|3[0-1])$", start_date)
        ):
            start_date = input(
                "Invalid date. Please enter a start date "
                + 'ranging from year 2000 in "yyyy-mm-dd" '
                + "format: "
            ).strip()
        end_date = input(
            'Please enter an end date ranging from year 2000 in "yyyy-mm-dd" format: '
        ).strip()
        while not bool(
            re.match("^20[0-2][0-9]-((0[1-9])|(1[0-2]))-([0-2][1-9]|3[0-1])$", end_date)
        ):
            end_date = input(
                "Invalid date. Please enter an end date "
                + 'ranging from year 2000 in "yyyy-mm-dd" '
                + "format: "
            ).strip()
        while not datetime.strptime(start_date, "%Y-%m-%d") < datetime.strptime(
            end_date, "%Y-%m-%d"
        ):
            end_date = input(
                "Please re-enter an end date that is greater than the start date: "
            ).strip()
            while not bool(
                re.match("^20[0-2][0-9]-((0[1-9])|(1[0-2]))-([0-2][1-9]|3[0-1])$", end_date)
            ):
                end_date = input(
                    "Please enter a start date ranging from "
                    + 'year 2000 in "yyyy-mm-dd" format: '
                ).strip()
        return start_date, end_date

    def save_geodataframe_to_csv(self, event_app):
        """
        Define start and end dates to process the earthquake event data
        sourced from GeoNet with an estimated affected polygon
        attached to each event, and stored in a CSV file.
        """
        start_date, end_date = self.input_dates()
        date_dict = self.create_date_range_dict(start_date, end_date)

        column_names = [
            "publicid",
            "eventtype",
            "origintime",
            "modificationtime",
            "depth",
            "magnitude",
            "magnitudetype",
            "evaluationmethod",
            "evaluationstatus",
            "evaluationmode",
            "earthmodel",
            "usedphasecount",
            "usedstationcount",
            "minimumdistance",
            "azimuthalgap",
            "magnitudeuncertainty",
            "originerror",
            "magnitudestationcount",
            "longitude",
            "latitude",
            "depthtype",
            "mmi",
            "locality",
            "quality",
            "geometry",
            "WKT",
        ]
        df = pd.DataFrame(columns=column_names)

        for key, value in date_dict.items():
            date_list = self.prepare_date_range(value[0], value[1])
            event_df = self.get_geonet_event(date_list, self.magnitude_theshold)
            if event_df.shape[0] > 0:
                event_gdf = event_app.convert_df_to_gdf(event_df, "longitude", "latitude")
                gdf = self.output_geodataframe_with_polygon(event_gdf, event_app)
                df = pd.concat([df, gdf]).reset_index(drop=True)
                print(f"{key} event data fetched successfully.")
        df = df[~df["WKT"].isnull()]
        self.setFolder(DATA_FOLDER)
        df.drop("geometry", axis=1).to_csv(
            os.path.join(DATA_FOLDER, f"events_{start_date}_{end_date}.csv"), index=False
        )
        print(
            f"Please find the file containing events from {start_date}"
            + f" to {end_date} with a magnitude of "
            + f"{self.magnitude_theshold} and above in the directory "
            + f"{os.path.abspath(os.path.join(os.getcwd(), DATA_FOLDER, f'events_{start_date}_{end_date}.csv'))}."
        )

def getFlag(flag):
    """
    Define whether a flag in the run argument and print the flag.
    """
    response = False
    if flag in sys.argv:
        response = True
    if response:
        print(f'main::gotThisFlag found {flag}')
    return response

def gotFetchFlag():
    """
    Define whether a flag "-f" in the run argument.
    """
    return getFlag('-f')

def gotGuiFlag():
    """
    Define whether a flag "-p" in the run argument.
    """
    return getFlag('-p')

def main():
    """
    Define whether a flag in the run argument.
    If flag "-f" in the run argument, fetch history event data program is going 
    to run. Source_History_Events class will be triggrted to source the history
    seismic event data.
    If flag "-p" in the run argument, plot visuals program is going to run. All
    Event_Contour_Map class, NZ_Addresses and Ui_MainWindow claases will be 
    triggrted to plot folium maps in a BI intelligent dashborad GUI window.
    """
    response = 1
    print(f'argv:{str(sys.argv)}')

    if gotFetchFlag():
        print('main gotFetchFlag')
        event_app = Event_Contour_Map()
        app = Source_History_Events(magnitude_theshold = 5, boundary_mmi = 3.5)
        response = app.save_geodataframe_to_csv(event_app)

    elif gotGuiFlag():
        print('main gotGuiFlag')
        event_app = Event_Contour_Map()
        event_data = event_app.read_gdf_from_wkt('events_2009-03-01_2024-03-01.csv')
        nz_address_gdf = event_app.read_gdf_from_wkt(NZ_ADDRESSES_FILE)
        app = QApplication(sys.argv)
        MainWindow = QMainWindow()
        ui = Ui_MainWindow(MainWindow, event_data, nz_address_gdf)
        MainWindow.show()
        sys.exit(app.exec_())

    return response

if __name__ == "__main__": 
    response = main()
    print(f'\nDONE - returning {response}')
    sys.exit(response)