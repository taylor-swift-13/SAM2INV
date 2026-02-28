int main49(int a,int k,int m){
  int l, y, v, j;

  l=k;
  y=l;
  v=-5;
  j=-6;

  while (y>0) {
      if (v+1<=l) {
          v = v+1;
      }
      else {
          v = l;
      }
      v = v+y;
      j = j*j;
  }

}
