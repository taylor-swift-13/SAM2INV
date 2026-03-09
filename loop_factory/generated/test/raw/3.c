int main1(int v){
  int mgq, qt, k;

  mgq=(v%7)+15;
  qt=0;
  k=-6;

  while (1) {
      if (!(qt<=mgq-1)) {
          break;
      }
      k = k + 3;
      v++;
      qt++;
  }

}
