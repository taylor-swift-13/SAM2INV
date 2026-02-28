int main1(int k,int m,int n,int p){
  int s, w, v, u;

  s=(p%14)+18;
  w=0;
  v=w;
  u=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 8*w;
  loop invariant u == m + 4*w*(w+1);
  loop invariant 0 <= w;
  loop invariant w <= s;
  loop invariant s == (p%14) + 18;
  loop invariant n == \at(n, Pre);
  loop invariant u == \at(m, Pre) + 4*w*(w+1);
  loop invariant p == \at(p, Pre);
  loop invariant s == ( \at(p,Pre) % 14) + 18;
  loop invariant w >= 0;
  loop assigns v, w, u;
*/
while (1) {
      if (w>=s) {
          break;
      }
      v = v+3;
      w = w+1;
      v = v+5;
      u = u+v;
  }

}
