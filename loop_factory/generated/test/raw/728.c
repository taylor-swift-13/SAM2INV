int main1(){
  int he, neq, yh0;

  he=0;
  neq=(1%28)+10;
  yh0=5;

  while (neq>he) {
      neq = neq - he;
      yh0 = yh0+(neq%6);
      he++;
  }

}
