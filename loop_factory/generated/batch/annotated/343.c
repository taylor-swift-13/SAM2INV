int main1(int b,int n){
  int o, f, c, v;

  o=67;
  f=o;
  c=f;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 67;

  loop invariant c <= o;
  loop invariant v == n;
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant b == \at(b, Pre) &&
                   n == \at(n, Pre) &&
                   v == \at(n, Pre);
  loop invariant c >= o;
  loop assigns c;
*/
while (c<o) {
      if (c<o) {
          c = c+1;
      }
      c = c+v+v;
      c = c+1;
  }

}
