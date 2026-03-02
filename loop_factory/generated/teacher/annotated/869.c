int main1(int a,int m){
  int h, s, r, q;

  h=23;
  s=h+5;
  r=m;
  q=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 23;
  loop invariant q == 2*r - m;
  loop invariant s >= h;
  loop invariant s <= 28;
  loop invariant m == \at(m, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant s <= h + 5;

  loop invariant (m == 0) ==> (r == 0);

  loop invariant a == \at(a,Pre) && m == \at(m,Pre) && h == 23 && s >= h && s <= h+5;

  loop invariant s >= h && s <= h + 5;
  loop invariant a == \at(a, Pre) && m == \at(m, Pre);


  loop assigns r, q, s;
*/
while (s>h) {
      r = r*2;
      q = q+r;
      s = s-1;
  }

}
