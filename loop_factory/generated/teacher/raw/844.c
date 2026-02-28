int main1(int b,int n,int p){
  int h, c, v, o, t;

  h=76;
  c=0;
  v=-48;
  o=h;
  t=b;

  while (v<=-2) {
      v = v+o+2;
      o = o+1;
      v = v+1;
      o = o+v;
      t = t+5;
      v = v+3;
  }

}
