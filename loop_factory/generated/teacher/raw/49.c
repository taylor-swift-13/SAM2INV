int main1(int k,int p){
  int h, o, v, s, w, x;

  h=(k%12)+16;
  o=0;
  v=h;
  s=k;
  w=k;
  x=2;

  while (o<h) {
      s = s+w;
      w = w+v;
      o = o+1;
  }

}
