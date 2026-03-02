int main1(int b,int p){
  int r, w, o;

  r=p;
  w=0;
  o=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == 0;
  loop invariant o == -8 || o == 0;
  loop invariant r == \at(p, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant o <= 0;
  loop invariant (w % 9) == 0;
  loop invariant r == \at(p,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant b == \at(b,Pre);
  loop invariant r == p;
  loop invariant w % 9 == 0;
  loop invariant ((w % 9) == 0 ==> (o == -8 || o == 0));
  loop invariant (w % 9 == 0) ==> (o == -8 || o == 0);
  loop invariant (w % 9 != 0) ==> (o <= -8);
  loop assigns o;
*/
while (1) {
      o = o+3;
      if ((w%9)==0) {
          o = o-o;
      }
      else {
          o = o-4;
      }
  }

}
