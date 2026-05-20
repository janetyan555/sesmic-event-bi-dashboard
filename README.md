# Sesmic Event BI Dashboard

New Zealand seismic history events data source and business intelligence 
dashboard for impact density map of each event and property addresses in 
New Zealand with correlated history seismic events visualization application, 
to visualise the impacted area and severity of a given event, and any NZ 
property address with Its historical correlated events.

## Outcome
Run either:
- -f to fetch seismic event history data
- -p to launch the BI dashboard

## Overview
This application provides a seismic event visualisation tool for New Zealand, combining GeoNet data with property address mapping.
It supports:
- Fetching historical seismic events and intensity data
- Generating affected area polygons
- Visualising event impact via an interactive BI dashboard

## Key Components
- Source_History_Events
  Fetches seismic event data, intensity (MMI), and station data from GeoNet APIs and outputs structured data.
- Event_Contour_Map
  Generates intensity contour maps using inverse distance weighting.
- NZ_Addresses
  Identifies and plots affected property addresses.
- Ui_MainWindow
  Provides a desktop GUI with integrated Folium visualisation.

## Installation
1. Clone repository
   git clone <your-repo-url>
   cd <your-repo-folder>
2. Install dependencies
   pip install -r requirements.txt

## Data Setup
Ensure the following files are available:
data/
├── nz-addresses_10000_sample.csv
├── nz.gpkg

Update paths in the script if needed:
  DATA_FOLDER = '../data'

## Usage
1. Fetch seismic event history data
   python seismicEventVisual.py -f

  What it does:
  - Calls GeoNet APIs
  - Retrieves earthquake events above threshold
  - Extracts intensity and station data
  - Generates processed dataset (CSV output)
  When to use:
  - First run
  - Data refresh
  - Updating event history

2. Run BI Dashboard
   python seismicEventVisual.py -p

  What it does:
  - Launches PyQt GUI
  - Displays Folium interactive maps
  - Visualises:
    - Seismic intensity contours
    - Affected regions
    - Property addresses linked to events
  When to use:
  - Data exploration
  - Stakeholder demonstration
  - Impact analysis

3. Optional: Combined workflow
  Run in sequence:
  - python seismicEventVisual.py -f
  - python seismicEventVisual.py -p

## Runtime Arguments
|Argument|Purpose|
|-f|Fetch and process seismic event history data|
|-p|Launch dashboard visualisation|

## Example Workflow
Fetch latest data:
  python seismicEventVisual.py -f

Launch dashboard:
  python seismicEventVisual.py -p

## Dependencies
See requirements.txt. Key libraries include:
- PyQt5
- geopandas
- shapely
- folium
- scipy
- matplotlib

## Notes and Limitations
- GeoNet API availability may affect data retrieval
- Geospatial libraries may require system level dependencies
- Large datasets may impact performance
