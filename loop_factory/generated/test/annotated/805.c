int main1(int x,int w){
  int hdp, vbp, mwo, qa5;
  hdp=w;
  vbp=0;
  mwo=5;
  qa5=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((qa5 - 1) % mwo == 0);
  loop invariant ((hdp == \at(w, Pre)) || (hdp == vbp));
  loop invariant (vbp == 0);
  loop invariant (hdp == vbp) || (qa5 == 1 && hdp == \at(w, Pre) && vbp == 0);
  loop assigns hdp, qa5;
*/
while (vbp+1<=hdp) {
      qa5 = qa5 + mwo;
      hdp = (vbp+1)-1;
  }
}