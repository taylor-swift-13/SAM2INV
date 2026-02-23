int main1(int k,int m){
  int o, x, v, w;

  o=m-9;
  x=0;
  v=k;
  w=-8;

  while (x<=o-1) {
      if (v+5<=o) {
          v = v+5;
      }
      else {
          v = o;
      }
      v = v+x;
  }

}
