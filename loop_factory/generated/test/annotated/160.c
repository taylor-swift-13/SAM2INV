int main1(){
  int ti;
  ti=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ti <= 1;
  loop assigns ti;
*/
while (ti!=ti) {
      if (ti>ti) {
          ti = ti - ti;
          ti = ti - ti;
          ti = ti - ti;
      }
      else {
          ti = ti - ti;
          ti = ti - ti;
          ti = ti - ti;
      }
      ti = ti%8;
  }
}