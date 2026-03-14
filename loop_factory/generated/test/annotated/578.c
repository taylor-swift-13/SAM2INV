int main1(){
  int zgbs, s, no;
  zgbs=1*2;
  s=1;
  no=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant no == 2*s - 2;
  loop invariant zgbs == 2;
  loop invariant no >= 0;
  loop assigns no, s;
*/
while (s<=zgbs) {
      no = (1)+(no);
      s = 2*s;
      no = no + no;
  }
}