int main1(){
  int n8, k0, qa, kmv, kk6, lu, dk, fs, p0;
  n8=46;
  k0=0;
  qa=k0;
  kmv=n8;
  kk6=n8;
  lu=k0;
  dk=1;
  fs=0;
  p0=k0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kk6 - fs == 46;
  loop invariant ((kmv - 46) % 5) == 0;
  loop invariant k0 == 0;
  loop invariant lu == 0;
  loop invariant qa >= 0;
  loop invariant kmv >= 46;
  loop invariant dk >= 1;
  loop invariant fs >= 0;
  loop invariant n8 >= 0;
  loop invariant p0 >= 0;
  loop invariant n8 <= 46;
  loop invariant k0 <= n8;
  loop assigns qa, dk, kmv, kk6, lu, fs, p0, n8;
*/
while (k0+1<=n8) {
      if (!(!(k0<n8/2))) {
          qa = qa + 1;
      }
      else {
          qa += kmv;
      }
      if (p0<p0+3) {
          dk += p0;
      }
      kmv = kmv + 5;
      kk6 += qa;
      lu = lu+(k0%2);
      fs += qa;
      p0 += qa;
      p0++;
      n8 = (k0+1)-1;
  }
}