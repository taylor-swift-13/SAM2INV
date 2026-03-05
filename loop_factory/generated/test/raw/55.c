int main1(int b){
  int iil, tj7j;

  iil=(b%39)+7;
  tj7j=0;

  while (tj7j<iil) {
      tj7j = 2*tj7j;
      tj7j += 1;
      b += iil;
  }

}
