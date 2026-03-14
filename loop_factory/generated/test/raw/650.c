int main1(int a,int l){
  int g, j, o2, np, db3, qqw;

  g=l*3;
  j=0;
  o2=1;
  np=0;
  db3=10;
  qqw=l;

  while (o2<=g) {
      np = np+o2*o2;
      o2 += 1;
      qqw += j;
  }

  while (j<qqw) {
      o2 = qqw-j;
      j++;
      db3 += j;
  }

}
