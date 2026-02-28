int main1(int b,int q){
  int f, z, c, w;

  f=58;
  z=2;
  c=b;
  w=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant f == 58;
  loop invariant (b <= f) ==> (c <= f);


  loop assigns c;
*/
while (1) {
      if (c+2<=f) {
          c = c+2;
      }
      else {
          c = f;
      }
  }

}
