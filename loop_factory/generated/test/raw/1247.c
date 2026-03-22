int main1(int z){
  int ouw, tg, r, ob, hv, f;

  ouw=z+5;
  tg=0;
  r=0;
  ob=1;
  hv=1;
  f=6;

  while (1) {
      if (!(ob<=ouw)) {
          break;
      }
      r = r + 1;
      hv += 2;
      f = f+(r%7);
      ob += hv;
      f = f + tg;
  }

}
