int main1(int m,int q){
  int w, v, o, l, r;

  w=m+8;
  v=w;
  o=0;
  l=6;
  r=w;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant w == \at(m, Pre) + 8;
  loop invariant v == w;
  loop invariant w == m + 8;
  loop invariant (w >= 0) ==> o >= 0;
  loop invariant (w >= 0) ==> l >= 6;
  loop invariant (w >= 0) ==> r >= w;
  loop assigns o, l, r;
*/
while (v-2>=0) {
      if (v<w/2) {
          o = o+l;
      }
      else {
          o = o+1;
      }
      l = l+r;
      r = r+o;
  }

}
