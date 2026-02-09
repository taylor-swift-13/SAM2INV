/*@ requires a % 2 == 0 && a > 0;*/
int main1(){

  int x, a, r;
  
  r = 0;
  x = a / 2;

  while (x > r){
        x = x - r;
        r = r + 1;
    }
  /*@ assert a == 2*x + r*r - r;*/
}

