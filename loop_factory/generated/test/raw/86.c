int main1(){
  int c, mp, y, eymz;

  c=1+11;
  mp=0;
  y=0;
  eymz=-6;

  while (y<c) {
      mp = (mp+1)%6;
      y++;
      eymz = eymz + y;
  }

}
