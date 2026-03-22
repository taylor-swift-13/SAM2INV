int main1(int s,int t){
  int qp, o6, o, jpu;
  qp=t;
  o6=0;
  o=s;
  jpu=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == \at(s, Pre);
  loop invariant o6 % 2 == 0;
  loop invariant o6 >= 0;
  loop invariant qp == t;
  loop invariant o <= s;
  loop assigns o6, o, s;
*/
while (1) {
      if (!(o6<qp)) {
          break;
      }
      o6 += 2;
      if (jpu<=o) {
          o = jpu;
      }
      s = s+o6-o6;
  }
}