int main1(){
  int hu0, i5, po2, bqo1;

  hu0=72;
  i5=0;
  po2=i5;
  bqo1=0;

  while (1) {
      if (!(i5 < hu0)) {
          break;
      }
      i5 += 1;
      po2 = po2 + i5 * i5;
      bqo1 = bqo1*2+(po2%6)+3;
  }

}
