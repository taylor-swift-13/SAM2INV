int main1(int b,int k){
  int v, o, j, z;

  v=b;
  o=v;
  j=o;
  z=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant o == v;
  loop invariant v <= j;
  loop invariant j <= v+1;
  loop invariant v == b;
  loop invariant j >= v;
  loop invariant v == \at(b, Pre);
  loop invariant v == o;
  loop invariant o == \at(b, Pre);
  loop invariant j >= \at(b, Pre);
  loop assigns j;
*/
while (o-1>=0) {
      if (j+3<=v) {
          j = j+3;
      }
      else {
          j = v;
      }
      j = j+1;
  }

}
