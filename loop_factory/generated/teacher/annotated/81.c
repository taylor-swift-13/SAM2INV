int main1(int k,int m){
  int e, y, v;

  e=k+24;
  y=0;
  v=e;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= y;
  loop invariant y <= e || e < 0;
  loop invariant v <= e;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant e == k + 24;
  loop invariant (y == 0) ==> (v == e);
  loop invariant (y > 0) ==> (v == 1);


  loop invariant y >= 0;
  loop invariant (((y == 0) ==> (v == e)) && ((y != 0) ==> (v == 1)));
  loop invariant (k == \at(k, Pre)) && (m == \at(m, Pre));
  loop assigns v, y;
*/
while (y<e) {
      v = v-v;
      if (y+1<=v+e) {
          v = v+1;
      }
      y = y+1;
  }

}
