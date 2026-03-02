int main1(int a,int b){
  int e, u, t;

  e=45;
  u=0;
  t=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant u == 0;
  loop invariant e == 45;
  loop invariant t >= 3;
  loop invariant e == 45 && u == 0;
  loop invariant t >= 3 && u <= e-1;
  loop invariant e == 45 && a == \at(a, Pre) && b == \at(b, Pre) && u == 0;
  loop invariant t > 0 && u <= e;
  loop invariant 0 <= u && u <= e;

  loop invariant t >= 3 && t > 0 && (u % 2) == 0 && u <= e - 1;
  loop invariant u == 0 && 0 <= u && u <= e;

  loop invariant u <= e;
  loop invariant u <= e - 1;
  loop invariant u % 2 == 0;
  loop assigns t;
*/
while (u<=e-1) {
      t = t+2;
      if ((u%2)==0) {
          t = t*t;
      }
      else {
          t = t*t+t;
      }
  }

}
