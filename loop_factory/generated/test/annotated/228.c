int main1(int w,int a){
  int umek, lr, eh;
  umek=22;
  lr=0;
  eh=umek;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eh == umek;
  loop invariant w == \at(w, Pre);
  loop invariant lr == 0;
  loop invariant umek == 22;
  loop invariant a == \at(a, Pre);
  loop assigns eh, w;
*/
while (eh<umek&&eh>0) {
      eh++;
      eh -= 1;
      w += lr;
  }
}