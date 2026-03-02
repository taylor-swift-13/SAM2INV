int main1(int a,int p){
  int u, v, j;

  u=p;
  v=0;
  j=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u == p;
  loop invariant j % 2 == 0;
  loop invariant v == 0 && u == p;
  loop invariant a == \at(a, Pre) && p == \at(p, Pre) && j >= 4 && (j % 2) == 0;
  loop invariant v == 0;
  loop invariant j >= 4;
  loop invariant a == \at(a, Pre) && p == \at(p, Pre) && u == p && v == 0 && j >= 4;
  loop invariant v == 0 && p == \at(p, Pre) && a == \at(a, Pre) && u == p;
  loop invariant j >= 4 && j % 2 == 0;
  loop invariant v == 0 && a == \at(a, Pre) && p == \at(p, Pre) && u == p;
  loop invariant j >= 4 && (j % 2) == 0;
  loop invariant v == 0 && j % 2 == 0;
  loop invariant j >= 4 && u == p && a == \at(a, Pre) && p == \at(p, Pre);
  loop assigns j;
*/
while (1) {
      j = j+3;
      if ((v%6)==0) {
          j = j+v;
      }
      j = j+j;
  }

}
