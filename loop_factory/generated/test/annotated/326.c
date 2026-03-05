int main1(){
  int qa;
  qa=(1%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qa >= 9;
  loop assigns qa;
*/
while (qa>0) {
      qa = qa+qa*qa;
  }
}