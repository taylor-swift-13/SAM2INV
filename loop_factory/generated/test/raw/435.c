int main1(int x,int m){
  int ow, t, alc, r4;

  ow=(m%39)+18;
  t=0;
  alc=0;
  r4=t;

  while (1) {
      if (!(alc<=ow-1)) {
          break;
      }
      alc++;
      x += ow;
      r4 = (ow)+(-(alc));
  }

  for (; t<=alc-1; t += 8) {
  }

}
