int main165(int k,int n,int p){
  int h, g, v, t;

  h=p+24;
  g=h;
  v=k;
  t=-2;

  while (g-1>=0) {
      v = v+4;
      g = g-1;
  }

  while (h<t) {
      v = t-g;
      g = g+1;
      v = v-1;
  }


  /*@ assert h >= t; */
}
