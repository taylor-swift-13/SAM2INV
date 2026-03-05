int main179(int r,int y,int b){
  int f, j6, dx8, fem, dj1, w, j;

  f=61;
  j6=1;
  dx8=0;
  fem=35;
  dj1=0;
  w=f;
  j=0;

  while (j6<=f) {
      j6 = 2*j6;
      dx8 = dx8 + 1;
      r += j6;
      b = b*2+(dx8%6)+2;
      y += b;
  }

  while (dj1<=fem-1) {
      dj1 = dj1 + 1;
      w += 2;
      r = r + 3;
      j = j + w;
      j++;
      r += j;
  }

}
