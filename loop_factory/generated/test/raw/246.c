int main1(){
  int j, ki;

  j=1;
  ki=0;

  while (ki<j) {
      if (ki<j/2) {
          ki += 1;
      }
      else {
          ki = ki - 1;
      }
      ki += 1;
      ki += ki;
  }

}
