int main4(int k,int p,int q){
  int l, f, g, j, v;

  l=p;
  f=0;
  g=(p%6)+2;
  j=p;
  v=l;

  while (v<l) {
      g = g*g+v;
      j = j*g;
      v = v+1;
  }

  while (f-1>=0) {
      if (g<=j) {
          j = g;
      }
      l = l+1;
      l = l+f;
      j = j*j;
  }


  /*@ assert f-1 < 0; */
}
