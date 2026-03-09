int main1(){
  int oy, q, x9p, u4, v8m;

  oy=102;
  q=oy;
  x9p=0;
  u4=q;
  v8m=q;

  while (1) {
      if (!(x9p<=oy-1)) {
          break;
      }
      x9p++;
      if (v8m<=u4) {
          u4 = v8m;
      }
      v8m = v8m + x9p;
  }

}
