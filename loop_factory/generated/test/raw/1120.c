int main1(){
  int q, t, z59, ijk, ok, de;

  q=1;
  t=0;
  z59=4;
  ijk=0;
  ok=t;
  de=q;

  while (ijk<q) {
      z59++;
      ijk = ijk + 1;
      ok += ijk;
  }

  while (1) {
      if (!(ok<ijk)) {
          break;
      }
      de = de+z59*ok;
      q = q+(de%5);
      ok = ijk;
  }

}
