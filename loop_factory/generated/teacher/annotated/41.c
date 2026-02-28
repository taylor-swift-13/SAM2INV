int main1(int k,int m){
  int d, q, e, v, o, h;

  d=68;
  q=0;
  e=0;
  v=m;
  o=q;
  h=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q >= 0 && q <= d;
  loop invariant (q == 0 && h == k) || (q >= 1 && h == e + v + o);
  loop invariant e == 0 && o == 0;
  loop invariant v == \at(m, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant 0 <= q && q <= d;
  loop invariant e == 0;
  loop invariant o == 0;
  loop invariant (q == 0) ==> (h == \at(k, Pre));
  loop invariant (q >= 1) ==> (h == e + v + o);
  loop invariant m == \at(m, Pre);
  loop invariant v == m;
  loop invariant h == k || h == e+v+o;
  loop invariant d == 68;
  loop invariant (q == 0 && h == k) || (q > 0 && h == e + v + o);
  loop invariant (q > 0) ==> (h == e + v + o);
  loop assigns h, q;
*/
while (q<d) {
      h = e+v+o;
      q = q+1;
  }

}
