int main1(int m,int q){
  int y, o, v;

  y=22;
  o=0;
  v=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant y == 22;
  loop invariant o >= 0;
  loop invariant v >= 0;
  loop invariant (v == 0) ==> (o == 0);
  loop invariant v <= (o*(o+1))/2;
  loop assigns v, o;
*/
while (1) {
      if (v+2<y) {
          v = v+o;
      }
      else {
          v = v-v;
      }
      v = v+1;
      o = o+1;
  }

}
