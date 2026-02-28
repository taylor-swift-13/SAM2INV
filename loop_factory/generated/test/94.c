int main94(int a,int b,int k){
  int w, x, s;

  w=b+3;
  x=0;
  s=-8;

  while (x<=w-1) {
      s = s+3;
      if (s+1<w) {
          s = s+s;
      }
      s = s+1;
      if (x+5<=b+w) {
          s = s+1;
      }
  }


  /*@ assert x > w-1; */
}
