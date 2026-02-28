int main19(int b,int k,int q){
  int h, m, l, o;

  h=b;
  m=0;
  l=k;
  o=-1;

  while (1) {
      l = l*2;
      o = o+l;
      o = o%6;
      l = l*2;
      m = m+1;
  }

  while (1) {
      o = o+h;
      m = m*m;
      h = h+1;
  }

  while (o!=0&&h!=0) {
      if (o>h) {
          o = o-h;
      }
      else {
          h = h-o;
      }
      o = o+h+h;
      o = o+1;
  }


  /*@ assert o == 0&&h!=0; */
}
