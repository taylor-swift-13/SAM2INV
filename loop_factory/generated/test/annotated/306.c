int main1(){
  int g8, i4, eeg;
  g8=50;
  i4=0;
  eeg=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eeg == 0;
  loop invariant 0 <= i4;
  loop invariant i4 <= g8;
  loop invariant g8 == 50;
  loop assigns eeg, i4;
*/
while (i4<g8) {
      if (eeg==0) {
          eeg += 1;
          eeg = eeg - 1;
          eeg = 1;
      }
      else {
          eeg = eeg - 1;
          eeg += 1;
          eeg = 0;
      }
      i4++;
      eeg = eeg - eeg;
  }
}