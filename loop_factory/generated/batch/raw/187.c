int main1(int m,int q){
  int w, v, o, l, r;

  w=m+8;
  v=w;
  o=0;
  l=6;
  r=w;

  while (v-2>=0) {
      if (v<w/2) {
          o = o+l;
      }
      else {
          o = o+1;
      }
      l = l+r;
      r = r+o;
  }

}
