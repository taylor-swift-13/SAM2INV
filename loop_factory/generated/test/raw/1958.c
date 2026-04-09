int main1(int d){
  int wkze, ui, go, x93l;

  wkze=(d%21)+17;
  ui=0;
  go=1;
  x93l=d;

  while (1) {
      if (!(ui < wkze)) {
          break;
      }
      go = (ui++, go * d);
      x93l += go;
      ui = wkze;
  }

}
