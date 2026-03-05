int main76(int h,int p,int v){
  int za, bg, yr5, k1, vv, lvg, w;

  za=h+19;
  bg=1;
  yr5=0;
  k1=(h%28)+10;
  vv=v;
  lvg=za;
  w=h;

  while (k1>yr5) {
      k1 -= yr5;
      yr5 = yr5 + 1;
      vv = vv+(k1%3);
      lvg = lvg+(yr5%9);
      h += 1;
      w = w + bg;
  }

}
