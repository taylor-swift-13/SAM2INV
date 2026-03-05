int main1(int o){
  int lu, ou3, it;
  lu=(o%17)+17;
  ou3=1;
  it=lu;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o >= \at(o, Pre);
  loop invariant ou3 == 1;
  loop invariant it >= lu;
  loop invariant lu == (\at(o, Pre) % 17) + 17;
  loop assigns it, o;
*/
while (ou3+1<=lu) {
      if (ou3<lu/2) {
          it = it + it;
      }
      else {
          it += 1;
      }
      o = o + lu;
  }
}