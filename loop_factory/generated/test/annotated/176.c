int main1(int a){
  int se8x, l9, l, dt, co, n;
  se8x=a;
  l9=0;
  l=43;
  dt=0;
  co=1;
  n=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l + dt == 43;
  loop invariant co - l9 == 1;
  loop invariant (0 <= l && l <= 43);
  loop invariant (0 <= dt && dt <= 43);
  loop invariant (0 <= l9);
  loop invariant (dt >= l9);
  loop invariant (0 <= n && n <= 43);
  loop invariant se8x == \at(a, Pre);
  loop invariant (se8x >= 0) ==> (l9 <= se8x);
  loop assigns l, dt, co, l9, n;
*/
while (1) {
      if (!(l>0&&l9<se8x)) {
          break;
      }
      if (l<=co) {
          n = l;
      }
      else {
          n = co;
      }
      l9 = l9 + 1;
      dt += n;
      co = co + 1;
      l -= n;
  }
}