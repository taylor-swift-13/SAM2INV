int main1(int e,int t){
  int re;
  re=17;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant re == 17;
  loop invariant e == \at(e, Pre);
  loop invariant t == \at(t, Pre);
  loop assigns re;
*/
while (re>0) {
      re += 1;
      re = re - 1;
  }
}