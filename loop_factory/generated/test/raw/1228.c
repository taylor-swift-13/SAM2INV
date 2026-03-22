int main1(){
  int uau1, me, hu, l, ol, ig;

  uau1=(1%19)+8;
  me=0;
  hu=0;
  l=me;
  ol=uau1;
  ig=uau1;

  while (1) {
      if (ig>uau1) {
          break;
      }
      hu += l;
      l = l + ol;
      hu = hu*2;
      ol = (4)+(ol);
      ig++;
  }

}
