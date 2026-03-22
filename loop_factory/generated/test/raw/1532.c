int main1(){
  int vmh, wx, e, j, m7k, ap, qj5, ek6;

  vmh=189;
  wx=0;
  e=vmh;
  j=vmh;
  m7k=vmh;
  ap=-3;
  qj5=wx;
  ek6=vmh;

  while (wx < vmh) {
      if (wx % 2 == 0) {
          e += 1;
          ek6++;
      }
      else {
          j++;
          m7k++;
      }
      wx += 1;
      if (!(!((wx%9)==0))) {
          ap += qj5;
      }
      ap += 2;
      qj5 += j;
      qj5 = qj5 + ap;
      qj5 += qj5;
  }

}
