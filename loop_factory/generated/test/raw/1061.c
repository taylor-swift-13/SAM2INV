int main1(){
  int em, mm, tc, ogr, ogmt;

  em=52;
  mm=em;
  tc=0;
  ogr=0;
  ogmt=4;

  while (1) {
      if (!(ogr<em)) {
          break;
      }
      ogmt = (ogmt+em)+(-(mm));
      tc += 1;
      ogr++;
      ogmt += mm;
  }

  while (1) {
      em += mm;
      mm = mm+(em%2);
      mm = mm + tc;
      ogmt++;
      if (ogmt>=ogr) {
          break;
      }
  }

}
