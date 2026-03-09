int main1(int s,int l){
  int z, pl, xzu, thr;

  z=l+22;
  pl=0;
  xzu=0;
  thr=l;

  while (1) {
      if (!(xzu<=z-1)) {
          break;
      }
      thr = thr + 3;
      pl = (pl+1)%7;
      xzu += 1;
      s = s + xzu;
  }

}
