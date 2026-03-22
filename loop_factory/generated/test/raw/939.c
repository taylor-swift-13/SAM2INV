int main1(){
  int dm, zt2, qj;

  dm=6;
  zt2=(1%20)+10;
  qj=(1%15)+8;

  while (zt2>0&&qj>0) {
      if (!(!(dm%2==0))) {
          zt2--;
      }
      else {
          qj--;
      }
      dm += 1;
  }

}
