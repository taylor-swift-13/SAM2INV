int main1(int l){
  int m, e, dx, b5, bv;

  m=l;
  e=0;
  dx=0;
  b5=0;
  bv=3;

  while (b5<m) {
      dx += l;
      b5++;
      l = l + m;
  }

  while (e!=0) {
      bv--;
      dx = dx + m;
      e = e - 1;
  }

}
