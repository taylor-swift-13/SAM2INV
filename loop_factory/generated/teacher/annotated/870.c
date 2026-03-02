int main1(int k,int m){
  int q, u, h, o;

  q=(k%10)+9;
  u=0;
  h=q;
  o=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h >= 0;
  loop invariant o >= 0;
  loop invariant h + o <= q;
  loop invariant q == (k % 10) + 9;
  loop invariant k == \at(k, Pre) && m == \at(m, Pre) && h >= 0 && o >= 0 && h + o <= q;
  loop invariant h <= q && o <= q;
  loop invariant 0 <= h && h <= q;
  loop invariant 0 <= o && o <= q;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant h >= 0 && o >= 0;

  loop invariant (h >= o) ==> (h - o) >= 0;
  loop invariant (o >= h) ==> (o - h) >= 0;
  loop invariant 0 <= h && 0 <= o && h <= q && o <= q && h + o <= q;
  loop invariant k == \at(k,Pre);
  loop invariant m == \at(m,Pre);
  loop assigns h, o;
*/
while (h!=0&&o!=0) {
      if (h>o) {
          h = h-o;
      }
      else {
          o = o-h;
      }
  }

}
