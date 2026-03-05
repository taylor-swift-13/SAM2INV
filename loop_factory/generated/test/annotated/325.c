int main1(){
  int jhu;
  jhu=(1%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jhu == 9 || jhu >= 90;
  loop assigns jhu;
*/
while (jhu>0) {
      jhu = jhu+jhu*jhu;
  }
}