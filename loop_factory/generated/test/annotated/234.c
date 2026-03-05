int main1(int s){
  int t5v, o4;
  t5v=s;
  o4=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t5v == \at(s, Pre);
  loop invariant s >= \at(s, Pre);
  loop invariant 0 <= o4;
  loop invariant o4 <= 4;
  loop assigns o4, s;
*/
while (o4<t5v) {
      o4 = (o4+1)%4;
      o4++;
      s = s + o4;
  }
}