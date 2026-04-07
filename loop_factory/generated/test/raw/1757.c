int main1(){
  int lwe, nt4, oh, qwo, o9, gu;

  lwe=(1%39)+4;
  nt4=0;
  oh=-3;
  qwo=0;
  o9=13;
  gu=lwe;

  while (1) {
      if (!(nt4 < lwe)) {
          break;
      }
      nt4 = ((oh = (qwo += (o9 += gu))), (nt4 + 1));
      o9 += gu;
      gu = gu+gu+o9;
      oh = oh*2;
  }

}
