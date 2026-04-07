int main1(int a){
  int res, j0, h, d;
  res=a-3;
  j0=res;
  h=res;
  d=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((h - res) * (a - 1) == d - 1);
  loop invariant (j0 - res == 0)  ==> (h == res);
  loop invariant (0 <= j0 - res);
  loop invariant res == a - 3;
  loop invariant j0 <= res;
  loop invariant (a == 1) ==> (h == j0);
  loop assigns h, j0, d;
*/
while (j0 < res) {
      h += d;
      j0++;
      d = d * a;
  }
}