int main1(){
  int oy, q, x9p, u4, v8m;
  oy=102;
  q=oy;
  x9p=0;
  u4=q;
  v8m=q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= x9p <= oy;
  loop invariant u4 == oy;
  loop invariant v8m == oy + x9p * (x9p + 1) / 2;
  loop assigns x9p, u4, v8m;
*/
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