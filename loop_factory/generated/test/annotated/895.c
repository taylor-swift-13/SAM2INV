int main1(int a){
  int ff, ej2, oo9t, rikf;
  ff=a+8;
  ej2=ff;
  oo9t=1;
  rikf=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rikf >= 0;
  loop invariant oo9t >= 1;
  loop invariant ff == \at(a, Pre) + 8;
  loop invariant ej2 == ff;
  loop invariant a == \at(a, Pre) + rikf * (ej2 + 1);
  loop invariant rikf <= oo9t;
  loop assigns rikf, a, oo9t;
*/
while (oo9t<=ff-1) {
      rikf += 1;
      a = a + ej2;
      oo9t = 2*oo9t;
      a++;
  }
}