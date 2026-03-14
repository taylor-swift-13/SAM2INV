int main1(){
  int yo, m, aha, a5;
  yo=1+7;
  m=yo;
  aha=m;
  a5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aha <= yo;
  loop invariant a5 == m * (aha - 8);
  loop invariant a5 == m * aha - m * m;
  loop invariant m == yo;
  loop assigns a5, aha;
*/
while (aha<yo) {
      a5 = a5 + m;
      aha++;
  }
}